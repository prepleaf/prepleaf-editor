import React from 'react';
import PropTypes from 'prop-types';
import DraftEditor from './DraftEditor';
import QuillEditor from './QuillEditor';

class PrepleafEditor extends React.Component {
	render() {
		if (this.props.htmlContent) {
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
