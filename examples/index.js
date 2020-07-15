import React from 'react';
import ReactDOM from 'react-dom';
import PrepleafEditor from '../src';

const rootElement = document.getElementById('root');

const apiBaseUrl = 'http://localhost:4040/api/questions';

const getImagePolicy = (file) => {
	const token = localStorage.getItem('token');
	return fetch(
		apiBaseUrl + '/get-question-image-upload-policy?name=' + file.name,
		{
			method: 'GET',
			headers: {
				Accept: 'application/json',
				'Content-Type': 'application/json',
				Authorization: 'Token ' + token,
			},
			credentials: 'include',
		}
	).then((res) => {
		if (res.ok) {
			return res.json();
		} else {
			throw Error('Error occurred');
		}
	});
};

class Example extends React.Component {
	constructor(props, context) {
		super(props, context);
		this.state = { readOnly: false, htmlContent: '<div>Hello</div>' };
	}
	render() {
		return (
			<div>
				<div>
					<label style={{ display: 'flex' }}>
						<input
							type="checkbox"
							value={this.state.readOnly}
							onChange={(e) => {
								this.setState({ readOnly: e.target.checked });
							}}
						/>
						<legend>Readonly</legend>
					</label>
					<PrepleafEditor
						rawContent={`{"blocks":[{"key":"ah5p3","text":"Hello","type":"unstyled","depth":0,"inlineStyleRanges":[],"entityRanges":[],"data":{}}],"entityMap":{}}`}
						getImagePolicy={getImagePolicy}
						readOnly={this.state.readOnly}
						customRef={this.handleDraftEditorRef}
					/>
					<button
						onClick={() => {
							console.log(JSON.stringify(this.draftEditorRef.value));
						}}
					>
						Get content
					</button>
				</div>
				<div>
					<textarea
						placeholder="Paste text here to see in editor"
						value={this.state.htmlContent}
						onChange={(e) => this.setState({ htmlContent: e.target.value })}
					></textarea>
					<PrepleafEditor
						customRef={this.handleQuillEditorRef}
						readOnly={this.state.readOnly}
						// htmlContent={this.state.htmlContent}
						rawContent={`{\"ops\":[{\"insert\":\"Hello\\nPrep\"},{\"attributes\":{\"bold\":true},\"insert\":\"leaf\"},{\"insert\":\"\\n\"}]}`}
					/>
					<button
						onClick={() => {
							console.log(JSON.stringify(this.quillEditorRef.value));
						}}
					>
						Get content
					</button>
				</div>
			</div>
		);
	}
	handleQuillEditorRef = (ref) => {
		this.quillEditorRef = ref;
	};
	handleDraftEditorRef = (ref) => {
		this.draftEditorRef = ref;
	};
}

ReactDOM.render(<Example />, rootElement);
