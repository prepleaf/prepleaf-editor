import React from 'react';
import PropTypes from 'prop-types';
import DraftEditor from './DraftEditor';
import QuillEditor from './QuillEditor';

const selectEditor = (props) => {
	if (props.htmlContent) {
		return 'Quill';
	}

	try {
		if (JSON.parse(props.rawContent).ops) {
			return 'Quill';
		} else {
		}
	} catch (e) {}

	return 'Draft';
};

class PrepleafEditor extends React.Component {
	constructor(props, context) {
		super(props, context);
		this.state = {
			editor: selectEditor(props),
		};
	}
	render() {
		if (this.state.editor === 'Quill') {
			return <QuillEditor {...this.props} />;
		} else {
			return <DraftEditor {...this.props} />;
		}
	}
}

PrepleafEditor.propTypes = {
	readOnly: PropTypes.bool.isRequired,
};

PrepleafEditor.defaultProps = {
	readOnly: false,
};

export default PrepleafEditor;
