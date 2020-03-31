import React from 'react';
import ReactDOM from 'react-dom';
import Editor from '../src';

const rootElement = document.getElementById('root');

const apiBaseUrl = 'http://localhost:4040/api/questions';

const getImagePolicy = file => {
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
	).then(res => {
		if (res.ok) {
			return res.json();
		} else {
			throw Error('Error occurred');
		}
	});
};

ReactDOM.render(React.createElement(Editor, { getImagePolicy }), rootElement);
